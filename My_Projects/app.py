import os
import subprocess
import requests
import json
import pyttsx3  # Local text-to-speech engine

# Output directory configuration
OUTPUT_DIR = "output_media"
os.makedirs(OUTPUT_DIR, exist_ok=True)


def generate_text_with_ollama(prompt):
    print("[+] 1. Generating text locally with Llama 3...")

    url = "http://localhost:11434/api/generate"
    data = {
        "model": "llama3:8b",
        "prompt": prompt,
        "stream": True
    }

    try:
        response = requests.post(url, json=data, stream=True, timeout=10)

        full_response = ""

        for line in response.iter_lines():
            if line:
                json_line = json.loads(line.decode("utf-8"))
                token = json_line.get("response", "")
                print(token, end="", flush=True)
                full_response += token

                if json_line.get("done", False):
                    break

        print("\n[✓] Text generation completed.")
        return full_response

    except Exception as e:
        print(f"\n[-] Ollama error: {e}")
        return "Stay safe online."


def generate_local_background():
    print("[+] 2. Generating a simple background image...")

    image_path = os.path.join(OUTPUT_DIR, "background_flat.jpg")

    # Create a solid-color background using FFmpeg
    cmd = [
        "ffmpeg",
        "-y",
        "-f",
        "lavfi",
        "-i",
        "color=c=0x1a1a2e:s=1280x720",
        "-vframes",
        "1",
        image_path,
    ]

    subprocess.run(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)

    return image_path


def create_real_voice(text):
    print("[+] 3. Converting text to speech locally...")

    audio_path = os.path.join(OUTPUT_DIR, "voice.mp3")

    # Initialize the TTS engine
    engine = pyttsx3.init()
    engine.setProperty("rate", 150)
    engine.setProperty("volume", 1.0)

    # Save speech to an audio file
    engine.save_to_file(text, audio_path)
    engine.runAndWait()

    if os.path.exists(audio_path):
        print("[✓] Voice generation completed.")
        return audio_path

    return None


def render_final_video(image, audio):
    print("[+] 4. Rendering the final video with FFmpeg...")

    video_output = os.path.join(OUTPUT_DIR, "final_video.mp4")

    ffmpeg_cmd = [
        "ffmpeg",
        "-y",
        "-loop",
        "1",
        "-i",
        image,
        "-i",
        audio,
        "-c:v",
        "libx264",
        "-tune",
        "stillimage",
        "-c:a",
        "aac",
        "-b:a",
        "192k",
        "-pix_fmt",
        "yuv420p",
        "-shortest",
        video_output,
    ]

    subprocess.run(ffmpeg_cmd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)

    if os.path.exists(video_output) and os.path.getsize(video_output) > 0:
        print(f"\n[★] Success! Final video saved to: {video_output}")
    else:
        print("\n[-] FFmpeg failed to render the final video.")


if __name__ == "__main__":
    print("=== Starting the Offline AI Video Pipeline ===")

    script = generate_text_with_ollama(
        "Write a short one-sentence cyber security rule."
    )

    background = generate_local_background()
    audio = create_real_voice(script)

    if background and audio:
        render_final_video(background, audio)