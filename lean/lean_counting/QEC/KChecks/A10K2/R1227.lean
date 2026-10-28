import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4908 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4908 = true := by
  decide +kernel

theorem tot4908 : totK PA10K2 A10K2.t4908 = [208628978462, 700016122871, 1416614165847, 1765873494701, 761338622300, 69778634372, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4909 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4909 = true := by
  decide +kernel

theorem tot4909 : totK PA10K2 A10K2.t4909 = [347958390714, 1678002046437, 2106288974714, 628790491693, 41635369674, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4910 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4910 = true := by
  decide +kernel

theorem tot4910 : totK PA10K2 A10K2.t4910 = [42959446034, 490793734168, 1781925076246, 1831221388371, 484558132624, 30831673886, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4911 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4911 = true := by
  decide +kernel

theorem tot4911 : totK PA10K2 A10K2.t4911 = [541634732801, 1943487983483, 1866161954385, 468588093913, 26491486257, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
