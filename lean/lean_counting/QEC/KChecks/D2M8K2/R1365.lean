import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5460 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5460 = true := by
  decide +kernel

theorem tot5460 : totK PD2M8K2 D2M8K2.t5460 = [0, 0, 0, 223529695821, 473708472331, 172635381399, 9417451333, 0] := by
  decide +kernel

theorem rows5461 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5461 = true := by
  decide +kernel

theorem tot5461 : totK PD2M8K2 D2M8K2.t5461 = [0, 0, 0, 240005029962, 488755227076, 168109472108, 7036466619, 0] := by
  decide +kernel

theorem rows5462 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5462 = true := by
  decide +kernel

theorem tot5462 : totK PD2M8K2 D2M8K2.t5462 = [0, 0, 0, 268812168049, 469828815112, 174317534515, 7107680034, 0] := by
  decide +kernel

theorem rows5463 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5463 = true := by
  decide +kernel

theorem tot5463 : totK PD2M8K2 D2M8K2.t5463 = [0, 0, 0, 202768095036, 486555251489, 187860609472, 8493418821, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
