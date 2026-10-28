import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14176 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14176 = true := by
  decide +kernel

theorem tot14176 : totK PD2M8K2 D2M8K2.t14176 = [0, 13888997881, 178308694784, 460533547887, 215889304046, 8969136212, 0, 0] := by
  decide +kernel

theorem rows14177 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14177 = true := by
  decide +kernel

theorem tot14177 : totK PD2M8K2 D2M8K2.t14177 = [0, 189976754637, 463458920540, 241849144496, 23089623618, 0, 0, 0] := by
  decide +kernel

theorem rows14178 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14178 = true := by
  decide +kernel

theorem tot14178 : totK PD2M8K2 D2M8K2.t14178 = [0, 181668098127, 470861933899, 220924292847, 12320791933, 0, 0, 0] := by
  decide +kernel

theorem rows14179 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14179 = true := by
  decide +kernel

theorem tot14179 : totK PD2M8K2 D2M8K2.t14179 = [0, 31007884993, 368261015081, 452115284826, 56427728826, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
