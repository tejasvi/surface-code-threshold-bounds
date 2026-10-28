import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows188 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t188 = true := by
  decide +kernel

theorem tot188 : totK PD2M8K2 D2M8K2.t188 = [0, 175892744135, 472674289810, 231414868803, 12169895203, 0, 0, 0] := by
  decide +kernel

theorem rows189 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t189 = true := by
  decide +kernel

theorem tot189 : totK PD2M8K2 D2M8K2.t189 = [0, 0, 280596309656, 512758207781, 86984461673, 1096505104, 0, 0] := by
  decide +kernel

theorem rows190 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t190 = true := by
  decide +kernel

theorem tot190 : totK PD2M8K2 D2M8K2.t190 = [0, 88185535531, 336944229197, 363909960062, 92952963274, 3838026431, 0, 0] := by
  decide +kernel

theorem rows191 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t191 = true := by
  decide +kernel

theorem tot191 : totK PD2M8K2 D2M8K2.t191 = [0, 188153733475, 445464161115, 246885847947, 20121790917, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
