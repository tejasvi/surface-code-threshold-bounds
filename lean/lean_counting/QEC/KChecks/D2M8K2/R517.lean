import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2068 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2068 = true := by
  decide +kernel

theorem tot2068 : totK PD2M8K2 D2M8K2.t2068 = [0, 0, 168452591775, 467335136027, 230957439900, 15635838661, 0, 0] := by
  decide +kernel

theorem rows2069 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2069 = true := by
  decide +kernel

theorem tot2069 : totK PD2M8K2 D2M8K2.t2069 = [0, 0, 180273317021, 470569037890, 228143274328, 13061323295, 0, 0] := by
  decide +kernel

theorem rows2070 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2070 = true := by
  decide +kernel

theorem tot2070 : totK PD2M8K2 D2M8K2.t2070 = [0, 0, 0, 311330439497, 451270244600, 86797426625, 1095107716, 0] := by
  decide +kernel

theorem rows2071 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2071 = true := by
  decide +kernel

theorem tot2071 : totK PD2M8K2 D2M8K2.t2071 = [0, 107685783034, 248505940659, 191578207351, 241922581973, 85322056683, 3882006667, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
