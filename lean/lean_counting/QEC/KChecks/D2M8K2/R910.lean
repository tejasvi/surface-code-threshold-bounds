import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3640 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3640 = true := by
  decide +kernel

theorem tot3640 : totK PD2M8K2 D2M8K2.t3640 = [0, 150083988337, 445585468370, 277899166147, 21715511011, 0, 0, 0] := by
  decide +kernel

theorem rows3641 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3641 = true := by
  decide +kernel

theorem tot3641 : totK PD2M8K2 D2M8K2.t3641 = [0, 0, 269784609028, 494412077758, 103893097927, 1310517177, 0, 0] := by
  decide +kernel

theorem rows3642 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3642 = true := by
  decide +kernel

theorem tot3642 : totK PD2M8K2 D2M8K2.t3642 = [0, 162618674105, 425290279251, 317530043785, 35524637297, 0, 0, 0] := by
  decide +kernel

theorem rows3643 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3643 = true := by
  decide +kernel

theorem tot3643 : totK PD2M8K2 D2M8K2.t3643 = [0, 175943407768, 472907565486, 248459938918, 14650459355, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
