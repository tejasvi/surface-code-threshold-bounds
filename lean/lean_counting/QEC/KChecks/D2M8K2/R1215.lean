import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4860 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4860 = true := by
  decide +kernel

theorem tot4860 : totK PD2M8K2 D2M8K2.t4860 = [0, 0, 34461480336, 273390937233, 405323812981, 182458904862, 18574160761, 0] := by
  decide +kernel

theorem rows4861 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4861 = true := by
  decide +kernel

theorem tot4861 : totK PD2M8K2 D2M8K2.t4861 = [0, 0, 0, 209774365607, 498943515054, 174855567872, 5019596775, 0] := by
  decide +kernel

theorem rows4862 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4862 = true := by
  decide +kernel

theorem tot4862 : totK PD2M8K2 D2M8K2.t4862 = [0, 0, 85554410256, 281309447901, 349745952256, 156522161439, 6557415438, 0] := by
  decide +kernel

theorem rows4863 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4863 = true := by
  decide +kernel

theorem tot4863 : totK PD2M8K2 D2M8K2.t4863 = [0, 0, 183174724504, 457162592628, 268542606390, 27345668608, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
