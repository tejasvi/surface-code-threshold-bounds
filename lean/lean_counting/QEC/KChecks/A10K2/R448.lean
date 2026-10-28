import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1792 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1792 = true := by
  decide +kernel

theorem tot1792 : totK PA10K2 A10K2.t1792 = [0, 0, 145729267903, 751129853037, 1718250654426, 1607619052818, 424462281573, 31768748853, 0, 0] := by
  decide +kernel

theorem rows1793 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1793 = true := by
  decide +kernel

theorem tot1793 : totK PA10K2 A10K2.t1793 = [0, 0, 403839006026, 1618325319766, 1938651514390, 660339580705, 52232171148, 0, 0, 0] := by
  decide +kernel

theorem rows1794 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1794 = true := by
  decide +kernel

theorem tot1794 : totK PA10K2 A10K2.t1794 = [0, 0, 283240155107, 1521235500881, 2098469649783, 805891274446, 60970094597, 0, 0, 0] := by
  decide +kernel

theorem rows1795 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1795 = true := by
  decide +kernel

theorem tot1795 : totK PA10K2 A10K2.t1795 = [0, 0, 0, 728638080878, 2166790613303, 1509225019565, 248335805736, 6354482628, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
