import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7768 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7768 = true := by
  decide +kernel

theorem tot7768 : totK PD2M8K2 D2M8K2.t7768 = [0, 0, 41466562539, 313726640506, 420796809536, 136250024429, 10536958543, 0] := by
  decide +kernel

theorem rows7769 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7769 = true := by
  decide +kernel

theorem tot7769 : totK PD2M8K2 D2M8K2.t7769 = [0, 0, 0, 268112393191, 496847321340, 145416635626, 2713714173, 0] := by
  decide +kernel

theorem rows7770 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7770 = true := by
  decide +kernel

theorem tot7770 : totK PD2M8K2 D2M8K2.t7770 = [0, 0, 171796794868, 424252818908, 246388544945, 49338778916, 3060566153, 0] := by
  decide +kernel

theorem rows7771 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7771 = true := by
  decide +kernel

theorem tot7771 : totK PD2M8K2 D2M8K2.t7771 = [0, 0, 192268762355, 458164930161, 230735924399, 16708320086, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
