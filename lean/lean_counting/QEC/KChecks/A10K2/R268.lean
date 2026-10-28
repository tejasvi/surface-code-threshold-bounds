import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1072 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1072 = true := by
  decide +kernel

theorem tot1072 : totK PA10K2 A10K2.t1072 = [0, 477575938760, 1858362407220, 1928609392271, 533827929700, 32256115688, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1073 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1073 = true := by
  decide +kernel

theorem tot1073 : totK PA10K2 A10K2.t1073 = [0, 226495846017, 1210350141823, 2134468223187, 1271122171998, 185663913252, 9729745405, 0, 0, 0] := by
  decide +kernel

theorem rows1074 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1074 = true := by
  decide +kernel

theorem tot1074 : totK PA10K2 A10K2.t1074 = [0, 185240259183, 864951910185, 1826276831248, 1578840058202, 403715462554, 21814044460, 0, 0, 0] := by
  decide +kernel

theorem rows1075 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1075 = true := by
  decide +kernel

theorem tot1075 : totK PA10K2 A10K2.t1075 = [0, 299663729046, 1529085487016, 2210340492356, 909767782678, 74174962135, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
