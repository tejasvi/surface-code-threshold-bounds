import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1876 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1876 = true := by
  decide +kernel

theorem tot1876 : totK PA10K2 A10K2.t1876 = [0, 0, 0, 591154504349, 1826904137932, 1730643008215, 533092391324, 48554111833, 0, 0] := by
  decide +kernel

theorem rows1877 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1877 = true := by
  decide +kernel

theorem tot1877 : totK PA10K2 A10K2.t1877 = [0, 0, 0, 43578157472, 1081049992370, 2296793597042, 1038243353021, 90853515237, 0, 0] := by
  decide +kernel

theorem rows1878 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1878 = true := by
  decide +kernel

theorem tot1878 : totK PA10K2 A10K2.t1878 = [0, 0, 0, 657551291554, 1858927421610, 1676691469670, 599156449222, 120824119802, 5528811039, 0] := by
  decide +kernel

theorem rows1879 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1879 = true := by
  decide +kernel

theorem tot1879 : totK PA10K2 A10K2.t1879 = [0, 0, 307513935741, 1145204826211, 1808445702113, 1319093182811, 371950811033, 29010686974, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
