import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2620 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2620 = true := by
  decide +kernel

theorem tot2620 : totK PD2M8K2 D2M8K2.t2620 = [0, 183285179032, 449247463040, 263651498765, 34873592041, 5773472233, 0, 0] := by
  decide +kernel

theorem rows2621 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2621 = true := by
  decide +kernel

theorem tot2621 : totK PD2M8K2 D2M8K2.t2621 = [0, 179951451417, 470896520400, 243646104737, 13813620715, 0, 0, 0] := by
  decide +kernel

theorem rows2622 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2622 = true := by
  decide +kernel

theorem tot2622 : totK PD2M8K2 D2M8K2.t2622 = [0, 86698232267, 323948321877, 361485424175, 141005283164, 15864095392, 0, 0] := by
  decide +kernel

theorem rows2623 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2623 = true := by
  decide +kernel

theorem tot2623 : totK PD2M8K2 D2M8K2.t2623 = [0, 0, 186698797447, 468010742396, 229160150161, 13530797253, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
