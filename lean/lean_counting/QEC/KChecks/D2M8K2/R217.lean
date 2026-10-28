import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows868 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t868 = true := by
  decide +kernel

theorem tot868 : totK PD2M8K2 D2M8K2.t868 = [0, 0, 178857416970, 466439463744, 237088546150, 13872966548, 0, 0] := by
  decide +kernel

theorem rows869 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t869 = true := by
  decide +kernel

theorem tot869 : totK PD2M8K2 D2M8K2.t869 = [0, 0, 180633332675, 475938449622, 205990382368, 7829432679, 0, 0] := by
  decide +kernel

theorem rows870 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t870 = true := by
  decide +kernel

theorem tot870 : totK PD2M8K2 D2M8K2.t870 = [0, 0, 196837133560, 464410517558, 197681080854, 13097073141, 0, 0] := by
  decide +kernel

theorem rows871 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t871 = true := by
  decide +kernel

theorem tot871 : totK PD2M8K2 D2M8K2.t871 = [0, 0, 113883862804, 439227516807, 294166005034, 22281945247, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
