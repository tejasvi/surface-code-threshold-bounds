import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1652 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1652 = true := by
  decide +kernel

theorem tot1652 : totK PD2M8K2 D2M8K2.t1652 = [0, 156729966339, 448000285183, 277976882325, 21427182598, 0, 0, 0] := by
  decide +kernel

theorem rows1653 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1653 = true := by
  decide +kernel

theorem tot1653 : totK PD2M8K2 D2M8K2.t1653 = [0, 0, 222488384229, 496272537744, 160601903446, 5768874209, 0, 0] := by
  decide +kernel

theorem rows1654 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1654 = true := by
  decide +kernel

theorem tot1654 : totK PD2M8K2 D2M8K2.t1654 = [0, 87240234242, 301802747569, 367263313955, 121287885760, 7474910654, 0, 0] := by
  decide +kernel

theorem rows1655 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1655 = true := by
  decide +kernel

theorem tot1655 : totK PD2M8K2 D2M8K2.t1655 = [0, 172770268313, 457951069351, 263749137558, 21925483537, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
