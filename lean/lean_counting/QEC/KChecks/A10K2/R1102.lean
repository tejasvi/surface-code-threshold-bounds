import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4408 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4408 = true := by
  decide +kernel

theorem tot4408 : totK PA10K2 A10K2.t4408 = [0, 0, 578253856154, 1859273496579, 1657355336158, 531469448428, 112576342320, 6354482628, 0, 0] := by
  decide +kernel

theorem rows4409 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4409 = true := by
  decide +kernel

theorem tot4409 : totK PA10K2 A10K2.t4409 = [0, 0, 180626633693, 1191139172916, 2106291464223, 1068519755393, 177200071720, 19313972475, 0, 0] := by
  decide +kernel

theorem rows4410 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4410 = true := by
  decide +kernel

theorem tot4410 : totK PA10K2 A10K2.t4410 = [0, 0, 196487554184, 866036007899, 1860787624618, 1441107884696, 282894203957, 10760911071, 0, 0] := by
  decide +kernel

theorem rows4411 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4411 = true := by
  decide +kernel

theorem tot4411 : totK PA10K2 A10K2.t4411 = [0, 0, 457260576693, 1817923633772, 1964972644739, 541313022137, 32411033166, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
