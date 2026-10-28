import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6128 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6128 = true := by
  decide +kernel

theorem tot6128 : totK PD2M8K2 D2M8K2.t6128 = [191401010580, 471901939080, 222081293875, 12373752831, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6129 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6129 = true := by
  decide +kernel

theorem tot6129 : totK PD2M8K2 D2M8K2.t6129 = [4187750769, 302548634524, 492202377902, 101183940049, 1164319620, 0, 0, 0] := by
  decide +kernel

theorem rows6130 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6130 = true := by
  decide +kernel

theorem tot6130 : totK PD2M8K2 D2M8K2.t6130 = [0, 193364890021, 474943362071, 190699655471, 11885407614, 0, 0, 0] := by
  decide +kernel

theorem rows6131 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6131 = true := by
  decide +kernel

theorem tot6131 : totK PD2M8K2 D2M8K2.t6131 = [179985095148, 461174791653, 238110458002, 20010436791, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
