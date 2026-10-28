import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13924 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13924 = true := by
  decide +kernel

theorem tot13924 : totK PD2M8K2 D2M8K2.t13924 = [89359567243, 346339011389, 390231142387, 86082566330, 1164319620, 0, 0, 0] := by
  decide +kernel

theorem rows13925 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13925 = true := by
  decide +kernel

theorem tot13925 : totK PD2M8K2 D2M8K2.t13925 = [0, 207009208861, 476059098710, 180135284028, 10241193787, 0, 0, 0] := by
  decide +kernel

theorem rows13926 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13926 = true := by
  decide +kernel

theorem tot13926 : totK PD2M8K2 D2M8K2.t13926 = [167218069055, 450617662875, 272588548343, 32855075394, 1503132863, 0, 0, 0] := by
  decide +kernel

theorem rows13927 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13927 = true := by
  decide +kernel

theorem tot13927 : totK PD2M8K2 D2M8K2.t13927 = [158517312710, 442387721130, 277947382825, 23094322095, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
