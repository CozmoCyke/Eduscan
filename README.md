# 📚 Eduscan — Intelligent PDF OCR & Comparison Lab  
**Version : Beta 20**

Eduscan est un laboratoire d’analyse et d’amélioration de documents PDF scannés et OCR, pensé pour les enseignants, chercheurs, archivistes, étudiants et passionnés de la qualité documentaire.

Contrairement aux outils classiques d’OCR, Eduscan ne se contente pas d’extraire du texte :
il **compare**, **corrige**, **évalue**, **fusionne intelligemment**, et aide à produire une **meilleure version textuelle** de vos documents.

---

## ✨ Fonctionnalités principales

### 🔍 Analyse intelligente de PDF
- Détection du type de PDF :
  - PDF natif
  - PDF image-only
  - PDF searchable (image + couche texte OCR)
- Extraction du texte intégré lorsque disponible
- Identification et extraction des images internes

---

## 🤖 OCR Comparatif
Eduscan supporte et compare plusieurs moteurs OCR :

| Moteur | Usage |
|--------|--------|
| 🔠 **Tesseract OCR** | Open-source, fiable, personnalisable |
| ☁ **Google Vision OCR** | Cloud, très haute précision |

Chaque résultat OCR est placé dans un onglet séparé pour permettre :
- lecture comparative,
- correction manuelle,
- analyse qualitative,
- scoring automatique.

---

## 🧠 Comparaison & Classement automatique
Eduscan attribue automatiquement un score aux différentes versions textuelles selon :
- lisibilité
- cohérence
- ponctuation
- stabilité structurelle

La meilleure version est automatiquement :
- marquée en **vert**
- considérée comme la *référence*
- utilisable dans les exports et futures améliorations

---

## 🧾 Exportation avancée
- 📄 Export TXT
- 🧾 Export Markdown (avec structures intelligentes)
- 📝 Export DOCX
- 🔎 Export PDF Searchable (nouvelle couche texte)

---

## 🧷 Fusion PDF — préserve la recherche !
Eduscan intègre une fonction de **fusion PDF lossless** :
- aucune perte de qualité
- pas de gonflement de fichier inutile
- conservation des couches OCR
- idéal pour fusionner plusieurs scans en un seul document fiable

---

## 🖼️ Gestion des images internes
- Extraction des schémas et images contenues dans le PDF
- Possibilité future d’insertion dans DOCX / HTML
- Base pour RAG / IA documentaire

---

## 🧪 Un vrai laboratoire d’analyse documentaire
Eduscan a été conçu pour aller bien plus loin que les outils classiques :
- il révèle *ce que ton PDF vaut réellement*
- il te montre *ce que l’OCR comprend*
- il te donne *le meilleur texte possible*
- il prépare les documents pour des usages IA avancés (RAG, compréhension sémantique, structuration)

---

## 🚀 Objectifs à venir
- Export intelligent multi-page (best per page)
- Reconstruction de structure pédagogique (cours chapitre → sous-sections → contenu)
- Export Google Docs
- OCR positionnel avancé
- Corrections morphologiques automatiques
- Pipeline RAG-ready

---

## ⚙️ Prérequis
- Python 3.10+
- Tesseract
- Poppler
- (optionnel) Google Vision API

---

## 👤 Auteur
Projet conçu et développé par **Cyke**, passionné d’éducation, d’IA et de reconstruction documentaire intelligente.

---

## 🧪 Statut
> Version actuelle : **BETA 20**  
Stable pour usage personnel et expérimentation — non encore destinée à la production académique officielle.

---

## ❤️ Pourquoi Eduscan existe ?
Parce qu’il n’existait **aucun outil** :
- capable d’analyser vraiment un PDF OCR,
- capable de comparer plusieurs OCR,
- capable de comprendre qu’un *searchable PDF* peut être meilleur qu’un OCR,
- capable de reconstruire un document compréhensible pour une IA.

Eduscan n’est pas “un autre scanner OCR”.
C’est une **station d’intelligence documentaire**.
