import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13788 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13788 = true := by
  decide +kernel

theorem tot13788 : totK PD2M8K2 D2M8K2.t13788 = [0, 203814164036, 464498208418, 187412265168, 11884213561, 0, 0, 0] := by
  decide +kernel

theorem rows13789 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13789 = true := by
  decide +kernel

theorem tot13789 : totK PD2M8K2 D2M8K2.t13789 = [197003158374, 448244893022, 243664885594, 29339417096, 0, 0, 0, 0] := by
  decide +kernel

theorem rows13790 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13790 = true := by
  decide +kernel

theorem tot13790 : totK PD2M8K2 D2M8K2.t13790 = [185782965217, 451063422565, 233656163012, 16792851761, 0, 0, 0, 0] := by
  decide +kernel

theorem rows13791 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13791 = true := by
  decide +kernel

theorem tot13791 : totK PD2M8K2 D2M8K2.t13791 = [19164099147, 340979373465, 460979998817, 73370542962, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
