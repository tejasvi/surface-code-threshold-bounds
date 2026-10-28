import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16192 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16192 = true := by
  decide +kernel

theorem tot16192 : totK PD2M8K2 D2M8K2.t16192 = [0, 0, 14614095730, 213179233887, 461499174007, 160929178007, 7682568795, 0] := by
  decide +kernel

theorem rows16193 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16193 = true := by
  decide +kernel

theorem tot16193 : totK PD2M8K2 D2M8K2.t16193 = [0, 0, 200136221350, 481208361029, 208388143304, 11071105621, 0, 0] := by
  decide +kernel

theorem rows16194 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16194 = true := by
  decide +kernel

theorem tot16194 : totK PD2M8K2 D2M8K2.t16194 = [0, 0, 104647262731, 407953734002, 313204094137, 37306228329, 1053411165, 0] := by
  decide +kernel

theorem rows16195 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16195 = true := by
  decide +kernel

theorem tot16195 : totK PD2M8K2 D2M8K2.t16195 = [0, 0, 84745114217, 385780446081, 379196853437, 39774117911, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
