import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5732 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5732 = true := by
  decide +kernel

theorem tot5732 : totK PA10K2 A10K2.t5732 = [0, 579887477939, 1882430770981, 1747151281626, 537020570987, 45595457238, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5733 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5733 = true := by
  decide +kernel

theorem tot5733 : totK PA10K2 A10K2.t5733 = [0, 166184698680, 1123853524920, 2111586803136, 1168566959571, 203981984087, 15171143123, 0, 0, 0] := by
  decide +kernel

theorem rows5734 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5734 = true := by
  decide +kernel

theorem tot5734 : totK PA10K2 A10K2.t5734 = [0, 122325564485, 733541033956, 1815692347512, 1662981799748, 369811695175, 16597605730, 0, 0, 0] := by
  decide +kernel

theorem rows5735 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5735 = true := by
  decide +kernel

theorem tot5735 : totK PA10K2 A10K2.t5735 = [0, 421700725875, 1676425367353, 1964462231413, 667535515412, 52232171148, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
