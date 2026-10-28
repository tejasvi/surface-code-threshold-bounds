import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15920 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15920 = true := by
  decide +kernel

theorem tot15920 : totK PD2M8K2 D2M8K2.t15920 = [0, 150052706404, 460848514323, 286338571114, 30216224072, 0, 0, 0] := by
  decide +kernel

theorem rows15921 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15921 = true := by
  decide +kernel

theorem tot15921 : totK PD2M8K2 D2M8K2.t15921 = [0, 0, 175806272580, 453396736036, 256136600464, 23760370731, 0, 0] := by
  decide +kernel

theorem rows15922 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15922 = true := by
  decide +kernel

theorem tot15922 : totK PD2M8K2 D2M8K2.t15922 = [0, 0, 183665782750, 498527403817, 214007456157, 6610549359, 0, 0] := by
  decide +kernel

theorem rows15923 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15923 = true := by
  decide +kernel

theorem tot15923 : totK PD2M8K2 D2M8K2.t15923 = [0, 167187563726, 421241736566, 249597366519, 67374635802, 5618966238, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
