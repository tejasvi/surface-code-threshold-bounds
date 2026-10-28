import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1708 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1708 = true := by
  decide +kernel

theorem tot1708 : totK PA10K2 A10K2.t1708 = [0, 0, 0, 477141004344, 1831764250487, 1883824232822, 490517721420, 30831673886, 0, 0] := by
  decide +kernel

theorem rows1709 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1709 = true := by
  decide +kernel

theorem tot1709 : totK PA10K2 A10K2.t1709 = [0, 0, 453345477736, 1681131858861, 1902050845727, 696173136662, 61352118366, 0, 0, 0] := by
  decide +kernel

theorem rows1710 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1710 = true := by
  decide +kernel

theorem tot1710 : totK PA10K2 A10K2.t1710 = [0, 0, 285599711294, 1452286121339, 2101132402630, 792476172384, 51330830718, 0, 0, 0] := by
  decide +kernel

theorem rows1711 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1711 = true := by
  decide +kernel

theorem tot1711 : totK PA10K2 A10K2.t1711 = [0, 0, 297783531355, 1100787759642, 1781272156703, 1211537534853, 203057512378, 6354482628, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
