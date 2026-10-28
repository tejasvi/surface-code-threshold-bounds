import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6876 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6876 = true := by
  decide +kernel

theorem tot6876 : totK PA10K2 A10K2.t6876 = [0, 314500777214, 1366328849100, 1979460941396, 1012112002065, 164725329633, 5460492893, 0, 0, 0] := by
  decide +kernel

theorem rows6877 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6877 = true := by
  decide +kernel

theorem tot6877 : totK PA10K2 A10K2.t6877 = [0, 267980227940, 1453080923108, 2100872439443, 797164709988, 52292001731, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6878 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6878 = true := by
  decide +kernel

theorem tot6878 : totK PA10K2 A10K2.t6878 = [0, 297510539734, 1245374072972, 1889308110209, 1096784886381, 180781229707, 5976421810, 0, 0, 0] := by
  decide +kernel

theorem rows6879 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6879 = true := by
  decide +kernel

theorem tot6879 : totK PA10K2 A10K2.t6879 = [0, 489237865208, 1860092855651, 2080748308417, 654452331047, 31541626609, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
