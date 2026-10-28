import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows136 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t136 = true := by
  decide +kernel

theorem tot136 : totK PD2M8K2 D2M8K2.t136 = [0, 0, 297285881719, 481342527616, 97406687408, 1067409660, 0, 0] := by
  decide +kernel

theorem rows137 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t137 = true := by
  decide +kernel

theorem tot137 : totK PD2M8K2 D2M8K2.t137 = [187240514448, 456566139768, 201334750755, 24676479370, 24313220081, 2814597007, 0, 0] := by
  decide +kernel

theorem rows138 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t138 = true := by
  decide +kernel

theorem tot138 : totK PD2M8K2 D2M8K2.t138 = [194273026388, 474587712508, 213696891214, 12526078277, 0, 0, 0, 0] := by
  decide +kernel

theorem rows139 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t139 = true := by
  decide +kernel

theorem tot139 : totK PD2M8K2 D2M8K2.t139 = [34113473973, 308586600811, 452273950128, 100239170603, 1369150432, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
