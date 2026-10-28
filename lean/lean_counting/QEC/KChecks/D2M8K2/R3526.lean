import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14104 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14104 = true := by
  decide +kernel

theorem tot14104 : totK PD2M8K2 D2M8K2.t14104 = [0, 0, 289261240307, 502776788363, 113075822654, 1249641317, 0, 0] := by
  decide +kernel

theorem rows14105 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14105 = true := by
  decide +kernel

theorem tot14105 : totK PD2M8K2 D2M8K2.t14105 = [0, 0, 205620691349, 481323121764, 185329844888, 7363658971, 0, 0] := by
  decide +kernel

theorem rows14106 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14106 = true := by
  decide +kernel

theorem tot14106 : totK PD2M8K2 D2M8K2.t14106 = [0, 0, 194057553096, 468491389745, 205898390317, 14707859566, 0, 0] := by
  decide +kernel

theorem rows14107 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14107 = true := by
  decide +kernel

theorem tot14107 : totK PD2M8K2 D2M8K2.t14107 = [0, 0, 256853978427, 473912733758, 180614127259, 17454128908, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
