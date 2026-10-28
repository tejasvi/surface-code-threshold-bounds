import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6132 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6132 = true := by
  decide +kernel

theorem tot6132 : totK PA10K2 A10K2.t6132 = [0, 0, 527488311110, 1885072802810, 1841405706755, 448529689769, 25668410676, 0, 0, 0] := by
  decide +kernel

theorem rows6133 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6133 = true := by
  decide +kernel

theorem tot6133 : totK PA10K2 A10K2.t6133 = [0, 0, 460758100454, 1792639120773, 1907724922009, 428953802423, 11323844185, 0, 0, 0] := by
  decide +kernel

theorem rows6134 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6134 = true := by
  decide +kernel

theorem tot6134 : totK PA10K2 A10K2.t6134 = [0, 115548944004, 167462220580, 748256332276, 2036083723844, 1281179272280, 193534632719, 5976421810, 0, 0] := by
  decide +kernel

theorem rows6135 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6135 = true := by
  decide +kernel

theorem tot6135 : totK PA10K2 A10K2.t6135 = [0, 501535388284, 1881616640986, 1947905377491, 536105814832, 31989350221, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
