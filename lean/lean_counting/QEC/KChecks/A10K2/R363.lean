import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1452 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1452 = true := by
  decide +kernel

theorem tot1452 : totK PA10K2 A10K2.t1452 = [0, 0, 105259173836, 704029974476, 1793196571406, 1647223859830, 432620555253, 30831673886, 0, 0] := by
  decide +kernel

theorem rows1453 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1453 = true := by
  decide +kernel

theorem tot1453 : totK PA10K2 A10K2.t1453 = [0, 0, 479693257008, 1781177459893, 1882464392846, 515459150460, 32846095359, 0, 0, 0] := by
  decide +kernel

theorem rows1454 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1454 = true := by
  decide +kernel

theorem tot1454 : totK PA10K2 A10K2.t1454 = [0, 0, 0, 593969421034, 2065277377675, 1667983078348, 271896681368, 5393623172, 0, 0] := by
  decide +kernel

theorem rows1455 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1455 = true := by
  decide +kernel

theorem tot1455 : totK PA10K2 A10K2.t1455 = [0, 0, 512579146014, 1783897043612, 1766931013426, 497365357408, 74876760080, 6034215561, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
