import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows708 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t708 = true := by
  decide +kernel

theorem tot708 : totK PD2M8K2 D2M8K2.t708 = [0, 243795337904, 497759753128, 158269604385, 5253830308, 0, 0, 0] := by
  decide +kernel

theorem rows709 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t709 = true := by
  decide +kernel

theorem tot709 : totK PD2M8K2 D2M8K2.t709 = [0, 163873467160, 454334352485, 231995060452, 16891742343, 0, 0, 0] := by
  decide +kernel

theorem rows710 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t710 = true := by
  decide +kernel

theorem tot710 : totK PD2M8K2 D2M8K2.t710 = [0, 154718827887, 462066443965, 245384422205, 15898197137, 0, 0, 0] := by
  decide +kernel

theorem rows711 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t711 = true := by
  decide +kernel

theorem tot711 : totK PD2M8K2 D2M8K2.t711 = [0, 0, 311008743125, 461793664853, 76948090371, 1138244013, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
