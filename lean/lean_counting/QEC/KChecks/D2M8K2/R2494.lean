import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9976 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9976 = true := by
  decide +kernel

theorem tot9976 : totK PD2M8K2 D2M8K2.t9976 = [0, 0, 0, 284336981401, 513405617720, 108171943371, 1178750802, 0] := by
  decide +kernel

theorem rows9977 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9977 = true := by
  decide +kernel

theorem tot9977 : totK PD2M8K2 D2M8K2.t9977 = [0, 0, 0, 198611445765, 474874447530, 186652871613, 11991925116, 0] := by
  decide +kernel

theorem rows9978 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9978 = true := by
  decide +kernel

theorem tot9978 : totK PD2M8K2 D2M8K2.t9978 = [0, 0, 195252417028, 453562206025, 235044543962, 19958790116, 0, 0] := by
  decide +kernel

theorem rows9979 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9979 = true := by
  decide +kernel

theorem tot9979 : totK PD2M8K2 D2M8K2.t9979 = [0, 0, 193977567649, 460321872339, 217538710763, 13422273528, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
