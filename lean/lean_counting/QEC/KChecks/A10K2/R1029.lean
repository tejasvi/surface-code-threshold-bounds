import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4116 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4116 = true := by
  decide +kernel

theorem tot4116 : totK PA10K2 A10K2.t4116 = [0, 669540932109, 2180924224827, 1865529984797, 356388605510, 6853348008, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4117 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4117 = true := by
  decide +kernel

theorem tot4117 : totK PA10K2 A10K2.t4117 = [0, 517354800115, 1759288950631, 1915826214042, 689744459067, 56143165367, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4118 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4118 = true := by
  decide +kernel

theorem tot4118 : totK PA10K2 A10K2.t4118 = [0, 513139438045, 1858212613740, 1955516069268, 523249613896, 31080743953, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4119 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4119 = true := by
  decide +kernel

theorem tot4119 : totK PA10K2 A10K2.t4119 = [0, 95320244489, 908336859878, 2136220579067, 1530609873475, 257778829322, 6904928264, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
