import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13456 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13456 = true := by
  decide +kernel

theorem tot13456 : totK PD2M8K2 D2M8K2.t13456 = [0, 0, 195213035499, 459420650783, 249245992807, 23175033022, 0, 0] := by
  decide +kernel

theorem rows13457 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13457 = true := by
  decide +kernel

theorem tot13457 : totK PD2M8K2 D2M8K2.t13457 = [0, 0, 183525682816, 473620299724, 232062000390, 13596035405, 0, 0] := by
  decide +kernel

theorem rows13458 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13458 = true := by
  decide +kernel

theorem tot13458 : totK PD2M8K2 D2M8K2.t13458 = [0, 0, 0, 295133860455, 469416667735, 141211105095, 9654694938, 0] := by
  decide +kernel

theorem rows13459 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13459 = true := by
  decide +kernel

theorem tot13459 : totK PD2M8K2 D2M8K2.t13459 = [0, 0, 64011344569, 258732051660, 406145696425, 156858038115, 5411637735, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
