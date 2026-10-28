import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13096 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13096 = true := by
  decide +kernel

theorem tot13096 : totK PD2M8K2 D2M8K2.t13096 = [0, 40345050560, 349098484061, 424680412425, 82159004916, 1096156699, 0, 0] := by
  decide +kernel

theorem rows13097 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13097 = true := by
  decide +kernel

theorem tot13097 : totK PD2M8K2 D2M8K2.t13097 = [0, 38156036945, 277992840218, 460519569070, 121697431399, 3880716147, 0, 0] := by
  decide +kernel

theorem rows13098 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13098 = true := by
  decide +kernel

theorem tot13098 : totK PD2M8K2 D2M8K2.t13098 = [0, 171710327241, 457821247632, 273122579481, 27806989793, 0, 0, 0] := by
  decide +kernel

theorem rows13099 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13099 = true := by
  decide +kernel

theorem tot13099 : totK PD2M8K2 D2M8K2.t13099 = [0, 177283396023, 465569791859, 244811461974, 13387598278, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
