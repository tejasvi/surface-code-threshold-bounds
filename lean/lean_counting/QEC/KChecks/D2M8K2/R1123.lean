import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4492 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4492 = true := by
  decide +kernel

theorem tot4492 : totK PD2M8K2 D2M8K2.t4492 = [0, 0, 200792483111, 479034454464, 216777701250, 14139338943, 0, 0] := by
  decide +kernel

theorem rows4493 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4493 = true := by
  decide +kernel

theorem tot4493 : totK PD2M8K2 D2M8K2.t4493 = [0, 0, 189411286772, 477254381875, 220332236567, 11046849895, 0, 0] := by
  decide +kernel

theorem rows4494 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4494 = true := by
  decide +kernel

theorem tot4494 : totK PD2M8K2 D2M8K2.t4494 = [0, 0, 180259805380, 486770111714, 233577607876, 10922721054, 0, 0] := by
  decide +kernel

theorem rows4495 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4495 = true := by
  decide +kernel

theorem tot4495 : totK PD2M8K2 D2M8K2.t4495 = [0, 0, 177234770963, 462239414093, 235558639230, 13781342912, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
