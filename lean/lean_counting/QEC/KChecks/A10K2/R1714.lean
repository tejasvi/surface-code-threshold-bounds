import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6856 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6856 = true := by
  decide +kernel

theorem tot6856 : totK PA10K2 A10K2.t6856 = [0, 587373109113, 1959484745863, 1813611444925, 431358405234, 25342575921, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6857 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6857 = true := by
  decide +kernel

theorem tot6857 : totK PA10K2 A10K2.t6857 = [0, 45274709553, 798930678940, 2107343773067, 1608468648926, 334619168626, 11991740650, 0, 0, 0] := by
  decide +kernel

theorem rows6858 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6858 = true := by
  decide +kernel

theorem tot6858 : totK PA10K2 A10K2.t6858 = [0, 298738363490, 1343929925821, 2031620421491, 1081836989544, 128789720981, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6859 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6859 = true := by
  decide +kernel

theorem tot6859 : totK PA10K2 A10K2.t6859 = [0, 466524748085, 1781136340461, 2042154276674, 643293084229, 39362433400, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
