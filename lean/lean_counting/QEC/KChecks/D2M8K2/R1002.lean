import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4008 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4008 = true := by
  decide +kernel

theorem tot4008 : totK PD2M8K2 D2M8K2.t4008 = [0, 0, 171133754129, 448044634920, 244501322576, 17628710678, 0, 0] := by
  decide +kernel

theorem rows4009 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4009 = true := by
  decide +kernel

theorem tot4009 : totK PD2M8K2 D2M8K2.t4009 = [0, 0, 89110402571, 365530358305, 348799759015, 61627436917, 1086231185, 0] := by
  decide +kernel

theorem rows4010 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4010 = true := by
  decide +kernel

theorem tot4010 : totK PD2M8K2 D2M8K2.t4010 = [0, 0, 0, 293668170849, 451448562882, 104012290753, 3752012233, 0] := by
  decide +kernel

theorem rows4011 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4011 = true := by
  decide +kernel

theorem tot4011 : totK PD2M8K2 D2M8K2.t4011 = [0, 0, 195854956453, 472481478450, 223377408343, 19258918686, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
