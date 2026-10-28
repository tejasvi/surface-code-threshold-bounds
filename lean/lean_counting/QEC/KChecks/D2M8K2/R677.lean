import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2708 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2708 = true := by
  decide +kernel

theorem tot2708 : totK PD2M8K2 D2M8K2.t2708 = [0, 106005114803, 435625114217, 319556994587, 26670459860, 0, 0, 0] := by
  decide +kernel

theorem rows2709 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2709 = true := by
  decide +kernel

theorem tot2709 : totK PD2M8K2 D2M8K2.t2709 = [0, 0, 294651552769, 508577537641, 101688400723, 1096505104, 0, 0] := by
  decide +kernel

theorem rows2710 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2710 = true := by
  decide +kernel

theorem tot2710 : totK PD2M8K2 D2M8K2.t2710 = [0, 166086422910, 379305723133, 258075240039, 82279607090, 3884009855, 0, 0] := by
  decide +kernel

theorem rows2711 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2711 = true := by
  decide +kernel

theorem tot2711 : totK PD2M8K2 D2M8K2.t2711 = [0, 157963332236, 444861170916, 282142838795, 28336356625, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
