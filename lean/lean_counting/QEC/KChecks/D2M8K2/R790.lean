import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3160 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3160 = true := by
  decide +kernel

theorem tot3160 : totK PD2M8K2 D2M8K2.t3160 = [0, 0, 325630702557, 519911903546, 74865536852, 0, 0, 0] := by
  decide +kernel

theorem rows3161 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3161 = true := by
  decide +kernel

theorem tot3161 : totK PD2M8K2 D2M8K2.t3161 = [0, 156769431526, 386023594789, 291660169671, 75353925329, 1415142070, 0, 0] := by
  decide +kernel

theorem rows3162 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3162 = true := by
  decide +kernel

theorem tot3162 : totK PD2M8K2 D2M8K2.t3162 = [0, 167449153002, 453479034445, 267834908575, 18939763806, 0, 0, 0] := by
  decide +kernel

theorem rows3163 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3163 = true := by
  decide +kernel

theorem tot3163 : totK PD2M8K2 D2M8K2.t3163 = [0, 92216530678, 413090214985, 361765321864, 42206396238, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
