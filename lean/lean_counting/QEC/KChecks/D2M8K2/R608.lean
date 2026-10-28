import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2432 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2432 = true := by
  decide +kernel

theorem tot2432 : totK PD2M8K2 D2M8K2.t2432 = [0, 0, 175870066236, 468391037818, 253704233159, 21439521408, 0, 0] := by
  decide +kernel

theorem rows2433 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2433 = true := by
  decide +kernel

theorem tot2433 : totK PD2M8K2 D2M8K2.t2433 = [0, 0, 189705913725, 457849956904, 236208420839, 17017285544, 0, 0] := by
  decide +kernel

theorem rows2434 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2434 = true := by
  decide +kernel

theorem tot2434 : totK PD2M8K2 D2M8K2.t2434 = [0, 0, 75904225969, 347736107148, 386494090520, 87567745934, 1242138600, 0] := by
  decide +kernel

theorem rows2435 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2435 = true := by
  decide +kernel

theorem tot2435 : totK PD2M8K2 D2M8K2.t2435 = [0, 0, 0, 228971811508, 469334012207, 154443872578, 7182288656, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
