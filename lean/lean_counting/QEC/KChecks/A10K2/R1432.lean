import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5728 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5728 = true := by
  decide +kernel

theorem tot5728 : totK PA10K2 A10K2.t5728 = [0, 0, 459254937784, 1425365107555, 1733514589530, 957459541706, 167861161288, 6121173289, 0, 0] := by
  decide +kernel

theorem rows5729 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5729 = true := by
  decide +kernel

theorem tot5729 : totK PA10K2 A10K2.t5729 = [0, 470021399381, 1465042778993, 1651213251942, 971437346426, 289656597379, 12760911900, 0, 0, 0] := by
  decide +kernel

theorem rows5730 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5730 = true := by
  decide +kernel

theorem tot5730 : totK PA10K2 A10K2.t5730 = [0, 272659432210, 1478142504251, 2146032385836, 796356951614, 57088819604, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5731 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5731 = true := by
  decide +kernel

theorem tot5731 : totK PA10K2 A10K2.t5731 = [0, 0, 480778143227, 1817444965440, 1840936613763, 478589647562, 30831673886, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
