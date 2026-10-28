import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6696 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6696 = true := by
  decide +kernel

theorem tot6696 : totK PD2M8K2 D2M8K2.t6696 = [0, 93159147314, 386621471497, 385081664134, 43753803084, 0, 0, 0] := by
  decide +kernel

theorem rows6697 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6697 = true := by
  decide +kernel

theorem tot6697 : totK PD2M8K2 D2M8K2.t6697 = [0, 171553832733, 442353768791, 259987260581, 21635235585, 0, 0, 0] := by
  decide +kernel

theorem rows6698 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6698 = true := by
  decide +kernel

theorem tot6698 : totK PD2M8K2 D2M8K2.t6698 = [0, 157042048713, 457879970200, 273776764438, 24112890285, 0, 0, 0] := by
  decide +kernel

theorem rows6699 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6699 = true := by
  decide +kernel

theorem tot6699 : totK PD2M8K2 D2M8K2.t6699 = [0, 0, 190996497809, 458242020916, 220926901901, 18317572719, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
