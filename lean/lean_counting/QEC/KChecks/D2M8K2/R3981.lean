import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15924 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15924 = true := by
  decide +kernel

theorem tot15924 : totK PD2M8K2 D2M8K2.t15924 = [0, 178229519835, 462204589792, 265736068958, 18980127547, 0, 0, 0] := by
  decide +kernel

theorem rows15925 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15925 = true := by
  decide +kernel

theorem tot15925 : totK PD2M8K2 D2M8K2.t15925 = [0, 0, 254323686353, 508953869929, 132248456770, 2309606161, 0, 0] := by
  decide +kernel

theorem rows15926 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15926 = true := by
  decide +kernel

theorem tot15926 : totK PD2M8K2 D2M8K2.t15926 = [0, 139973194914, 391622177321, 290388872838, 79846217759, 5511322840, 0, 0] := by
  decide +kernel

theorem rows15927 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15927 = true := by
  decide +kernel

theorem tot15927 : totK PD2M8K2 D2M8K2.t15927 = [0, 168018233182, 439336806392, 280701862282, 30315036932, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
