import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8012 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8012 = true := by
  decide +kernel

theorem tot8012 : totK PA10K2 A10K2.t8012 = [0, 0, 68933609069, 737359467644, 2068468741689, 1761457584247, 364444303156, 12681556880, 0, 0] := by
  decide +kernel

theorem rows8013 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8013 = true := by
  decide +kernel

theorem tot8013 : totK PA10K2 A10K2.t8013 = [0, 0, 471823694318, 1829140193647, 2009399707173, 583701302501, 40407449475, 0, 0, 0] := by
  decide +kernel

theorem rows8014 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8014 = true := by
  decide +kernel

theorem tot8014 : totK PA10K2 A10K2.t8014 = [0, 0, 327737319032, 1534070067901, 2177865611691, 905845633598, 74993309784, 0, 0, 0] := by
  decide +kernel

theorem rows8015 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8015 = true := by
  decide +kernel

theorem tot8015 : totK PA10K2 A10K2.t8015 = [0, 0, 0, 534291617921, 1964335172968, 2024829092879, 463885007885, 13816090359, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
