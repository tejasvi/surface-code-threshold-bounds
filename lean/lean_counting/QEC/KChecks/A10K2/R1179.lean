import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4716 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4716 = true := by
  decide +kernel

theorem tot4716 : totK PA10K2 A10K2.t4716 = [0, 0, 467092711113, 1866762905040, 1925421296400, 485079371858, 26521581199, 0, 0, 0] := by
  decide +kernel

theorem rows4717 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4717 = true := by
  decide +kernel

theorem tot4717 : totK PA10K2 A10K2.t4717 = [0, 0, 0, 832122170562, 2346723976649, 1292932522566, 101799498308, 0, 0, 0] := by
  decide +kernel

theorem rows4718 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4718 = true := by
  decide +kernel

theorem tot4718 : totK PA10K2 A10K2.t4718 = [0, 0, 0, 588467729880, 1981606937127, 1713017359860, 321057424432, 12477276923, 0, 0] := by
  decide +kernel

theorem rows4719 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4719 = true := by
  decide +kernel

theorem tot4719 : totK PA10K2 A10K2.t4719 = [0, 0, 0, 454550888228, 1783744102999, 1938926018895, 505278928081, 26116334861, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
