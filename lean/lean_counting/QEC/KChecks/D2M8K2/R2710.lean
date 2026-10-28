import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10840 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10840 = true := by
  decide +kernel

theorem tot10840 : totK PD2M8K2 D2M8K2.t10840 = [0, 87089311879, 361322285354, 366261117386, 69764525274, 1369150432, 0, 0] := by
  decide +kernel

theorem rows10841 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10841 = true := by
  decide +kernel

theorem tot10841 : totK PD2M8K2 D2M8K2.t10841 = [0, 8225356785, 308495641693, 510746298839, 74534664497, 0, 0, 0] := by
  decide +kernel

theorem rows10842 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10842 = true := by
  decide +kernel

theorem tot10842 : totK PD2M8K2 D2M8K2.t10842 = [0, 172333458166, 440074045432, 274465357443, 29506060849, 0, 0, 0] := by
  decide +kernel

theorem rows10843 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10843 = true := by
  decide +kernel

theorem tot10843 : totK PD2M8K2 D2M8K2.t10843 = [0, 227552335857, 497560686281, 196936773988, 7489204129, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
