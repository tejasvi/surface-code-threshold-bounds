import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7160 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7160 = true := by
  decide +kernel

theorem tot7160 : totK PD2M8K2 D2M8K2.t7160 = [0, 177806637211, 470388285759, 236697935231, 13262355368, 0, 0, 0] := by
  decide +kernel

theorem rows7161 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7161 = true := by
  decide +kernel

theorem tot7161 : totK PD2M8K2 D2M8K2.t7161 = [0, 0, 289103254767, 510165177958, 97728538369, 1096505104, 0, 0] := by
  decide +kernel

theorem rows7162 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7162 = true := by
  decide +kernel

theorem tot7162 : totK PD2M8K2 D2M8K2.t7162 = [0, 0, 231187067074, 499083887226, 162337051534, 5253830308, 0, 0] := by
  decide +kernel

theorem rows7163 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7163 = true := by
  decide +kernel

theorem tot7163 : totK PD2M8K2 D2M8K2.t7163 = [0, 0, 168692678896, 459886479480, 215396779055, 14344490487, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
