import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows920 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t920 = true := by
  decide +kernel

theorem tot920 : totK PD2M8K2 D2M8K2.t920 = [0, 203410982109, 463824677059, 209659219442, 12595094539, 0, 0, 0] := by
  decide +kernel

theorem rows921 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t921 = true := by
  decide +kernel

theorem tot921 : totK PD2M8K2 D2M8K2.t921 = [0, 172058575686, 489109683937, 220487680986, 7212439438, 0, 0, 0] := by
  decide +kernel

theorem rows922 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t922 = true := by
  decide +kernel

theorem tot922 : totK PD2M8K2 D2M8K2.t922 = [0, 177621856571, 470378824734, 217616131134, 13501157342, 0, 0, 0] := by
  decide +kernel

theorem rows923 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t923 = true := by
  decide +kernel

theorem tot923 : totK PD2M8K2 D2M8K2.t923 = [0, 202127283896, 483506349781, 205860934258, 8091478096, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
