import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows684 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t684 = true := by
  decide +kernel

theorem tot684 : totK PA10K2 A10K2.t684 = [0, 211861399205, 755251144029, 1250015453201, 1507986133176, 878580587596, 162399198314, 6121173289, 0, 0] := by
  decide +kernel

theorem rows685 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t685 = true := by
  decide +kernel

theorem tot685 : totK PA10K2 A10K2.t685 = [0, 463161708194, 1752104357940, 1946732970312, 551784169447, 32040661968, 0, 0, 0, 0] := by
  decide +kernel

theorem rows686 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t686 = true := by
  decide +kernel

theorem tot686 : totK PA10K2 A10K2.t686 = [0, 67600016556, 855414843189, 1970548476182, 1468283339591, 338789022730, 25371180993, 0, 0, 0] := by
  decide +kernel

theorem rows687 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t687 = true := by
  decide +kernel

theorem tot687 : totK PA10K2 A10K2.t687 = [0, 283150731151, 1215831600930, 1868740151979, 1129684539186, 174707405591, 5460492893, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
