import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2600 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2600 = true := by
  decide +kernel

theorem tot2600 : totK PA10K2 A10K2.t2600 = [0, 471389460189, 1876098682718, 1897014132969, 453700238911, 25686058060, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2601 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2601 = true := by
  decide +kernel

theorem tot2601 : totK PA10K2 A10K2.t2601 = [0, 187747219659, 1052872152675, 2007291061630, 1282463281489, 266498848172, 20070762815, 0, 0, 0] := by
  decide +kernel

theorem rows2602 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2602 = true := by
  decide +kernel

theorem tot2602 : totK PA10K2 A10K2.t2602 = [0, 212862030042, 916141675837, 1803026575901, 1493107262264, 307711353517, 10747604052, 0, 0, 0] := by
  decide +kernel

theorem rows2603 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2603 = true := by
  decide +kernel

theorem tot2603 : totK PA10K2 A10K2.t2603 = [0, 454867602579, 1679035715743, 1886372520547, 628317774143, 51464731716, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
