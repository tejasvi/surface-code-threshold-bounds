import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15880 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15880 = true := by
  decide +kernel

theorem tot15880 : totK PD2M8K2 D2M8K2.t15880 = [0, 0, 0, 261315955881, 488481418481, 128235168594, 2318623666, 0] := by
  decide +kernel

theorem rows15881 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15881 = true := by
  decide +kernel

theorem tot15881 : totK PD2M8K2 D2M8K2.t15881 = [0, 0, 57196784527, 251732515892, 381282280901, 150710973510, 10786826731, 0] := by
  decide +kernel

theorem rows15882 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15882 = true := by
  decide +kernel

theorem tot15882 : totK PD2M8K2 D2M8K2.t15882 = [0, 0, 158585590079, 474705401275, 232489304057, 12084350913, 0, 0] := by
  decide +kernel

theorem rows15883 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15883 = true := by
  decide +kernel

theorem tot15883 : totK PD2M8K2 D2M8K2.t15883 = [0, 0, 178569747216, 465704335632, 235568267255, 14982019003, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
