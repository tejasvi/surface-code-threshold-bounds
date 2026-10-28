import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5244 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5244 = true := by
  decide +kernel

theorem tot5244 : totK PA10K2 A10K2.t5244 = [0, 0, 0, 512448787220, 1857788199135, 1785216133539, 456707232408, 30637645759, 0, 0] := by
  decide +kernel

theorem rows5245 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5245 = true := by
  decide +kernel

theorem tot5245 : totK PA10K2 A10K2.t5245 = [0, 0, 0, 111369051068, 1295030320066, 2244287229208, 844590168576, 63645606988, 0, 0] := by
  decide +kernel

theorem rows5246 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5246 = true := by
  decide +kernel

theorem tot5246 : totK PA10K2 A10K2.t5246 = [0, 0, 414273244854, 1377095545765, 1431968113581, 861686087984, 567029672850, 128644302662, 5676195732, 0] := by
  decide +kernel

theorem rows5247 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5247 = true := by
  decide +kernel

theorem tot5247 : totK PA10K2 A10K2.t5247 = [0, 0, 392143281965, 1684105524571, 2048638458523, 721172420068, 48333783177, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
