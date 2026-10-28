import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8784 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8784 = true := by
  decide +kernel

theorem tot8784 : totK PD2M8K2 D2M8K2.t8784 = [0, 63649779940, 244053932488, 399499124856, 165422881233, 10902245252, 0, 0] := by
  decide +kernel

theorem rows8785 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8785 = true := by
  decide +kernel

theorem tot8785 : totK PD2M8K2 D2M8K2.t8785 = [0, 178196242396, 463255920433, 248727123713, 23193760017, 0, 0, 0] := by
  decide +kernel

theorem rows8786 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8786 = true := by
  decide +kernel

theorem tot8786 : totK PD2M8K2 D2M8K2.t8786 = [0, 186845441936, 457429812571, 234982993421, 17036558032, 0, 0, 0] := by
  decide +kernel

theorem rows8787 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8787 = true := by
  decide +kernel

theorem tot8787 : totK PD2M8K2 D2M8K2.t8787 = [0, 0, 323976868808, 474263987680, 90204013324, 1096505104, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
