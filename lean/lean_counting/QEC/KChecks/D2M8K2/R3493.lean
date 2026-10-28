import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13972 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13972 = true := by
  decide +kernel

theorem tot13972 : totK PD2M8K2 D2M8K2.t13972 = [0, 0, 204752507504, 485061947271, 178313324481, 4627616211, 0, 0] := by
  decide +kernel

theorem rows13973 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13973 = true := by
  decide +kernel

theorem tot13973 : totK PD2M8K2 D2M8K2.t13973 = [0, 0, 150599342317, 441162300161, 297147789470, 29771932507, 0, 0] := by
  decide +kernel

theorem rows13974 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13974 = true := by
  decide +kernel

theorem tot13974 : totK PD2M8K2 D2M8K2.t13974 = [0, 0, 188737975751, 466939690346, 233921613392, 14955552507, 0, 0] := by
  decide +kernel

theorem rows13975 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13975 = true := by
  decide +kernel

theorem tot13975 : totK PD2M8K2 D2M8K2.t13975 = [0, 0, 158626312622, 464321676201, 271223204828, 24103214753, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
