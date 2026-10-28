import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10208 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10208 = true := by
  decide +kernel

theorem tot10208 : totK PD2M8K2 D2M8K2.t10208 = [0, 164257180446, 438164719553, 267303678008, 21224252509, 0, 0, 0] := by
  decide +kernel

theorem rows10209 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10209 = true := by
  decide +kernel

theorem tot10209 : totK PD2M8K2 D2M8K2.t10209 = [0, 92232705550, 342198266868, 381793633638, 81958078158, 1268739303, 0, 0] := by
  decide +kernel

theorem rows10210 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10210 = true := by
  decide +kernel

theorem tot10210 : totK PD2M8K2 D2M8K2.t10210 = [0, 0, 232717844250, 490039508765, 157985418827, 3148467853, 0, 0] := by
  decide +kernel

theorem rows10211 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10211 = true := by
  decide +kernel

theorem tot10211 : totK PD2M8K2 D2M8K2.t10211 = [0, 0, 183429468002, 474244697338, 222538154571, 12892459792, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
