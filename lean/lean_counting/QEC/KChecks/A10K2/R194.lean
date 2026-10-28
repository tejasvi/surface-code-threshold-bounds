import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows776 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t776 = true := by
  decide +kernel

theorem tot776 : totK PA10K2 A10K2.t776 = [0, 0, 42030787920, 555562624928, 1738877770978, 1683573416205, 467146507189, 30605747850, 0, 0] := by
  decide +kernel

theorem rows777 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t777 = true := by
  decide +kernel

theorem tot777 : totK PA10K2 A10K2.t777 = [0, 0, 592701873901, 1851364275884, 1748513814880, 459891097241, 30954851499, 0, 0, 0] := by
  decide +kernel

theorem rows778 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t778 = true := by
  decide +kernel

theorem tot778 : totK PA10K2 A10K2.t778 = [0, 0, 0, 1013102521119, 2342591552068, 1102742202290, 97111396872, 0, 0, 0] := by
  decide +kernel

theorem rows779 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t779 = true := by
  decide +kernel

theorem tot779 : totK PA10K2 A10K2.t779 = [0, 0, 675266114995, 1902681433241, 1659717874194, 585563350844, 114566238167, 5528811039, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
