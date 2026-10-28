import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows364 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t364 = true := by
  decide +kernel

theorem tot364 : totK PA10K2 A10K2.t364 = [0, 0, 527657368288, 1859950650045, 1957629552388, 606225089978, 49165311630, 0, 0, 0] := by
  decide +kernel

theorem rows365 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t365 = true := by
  decide +kernel

theorem tot365 : totK PA10K2 A10K2.t365 = [0, 0, 526682628925, 1864647103862, 1844353442223, 477722466830, 31222411477, 0, 0, 0] := by
  decide +kernel

theorem rows366 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t366 = true := by
  decide +kernel

theorem tot366 : totK PA10K2 A10K2.t366 = [0, 0, 0, 702892886642, 2103350371518, 1606257026571, 379613395024, 25239774317, 0, 0] := by
  decide +kernel

theorem rows367 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t367 = true := by
  decide +kernel

theorem tot367 : totK PA10K2 A10K2.t367 = [0, 0, 289478139766, 1289813248549, 1890224565261, 1045083696552, 178196365135, 5410721913, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
