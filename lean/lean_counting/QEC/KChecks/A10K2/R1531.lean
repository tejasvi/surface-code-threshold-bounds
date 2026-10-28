import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6124 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6124 = true := by
  decide +kernel

theorem tot6124 : totK PA10K2 A10K2.t6124 = [0, 576996404534, 1850724817425, 1653549588426, 507094978206, 208191171381, 34954726192, 0, 0, 0] := by
  decide +kernel

theorem rows6125 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6125 = true := by
  decide +kernel

theorem tot6125 : totK PA10K2 A10K2.t6125 = [0, 218412668081, 1346618136397, 2314293656101, 1040560558847, 79805878249, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6126 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6126 = true := by
  decide +kernel

theorem tot6126 : totK PA10K2 A10K2.t6126 = [0, 0, 484990952390, 1842967175751, 1867986723519, 481869236370, 30831673886, 0, 0, 0] := by
  decide +kernel

theorem rows6127 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6127 = true := by
  decide +kernel

theorem tot6127 : totK PA10K2 A10K2.t6127 = [0, 293307099335, 1217667372051, 1818267120138, 1081601566567, 200877110957, 6034215561, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
