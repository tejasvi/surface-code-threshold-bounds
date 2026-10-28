import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15056 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15056 = true := by
  decide +kernel

theorem tot15056 : totK PD2M8K2 D2M8K2.t15056 = [0, 0, 154317133126, 456940787023, 252638085500, 13904256362, 0, 0] := by
  decide +kernel

theorem rows15057 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15057 = true := by
  decide +kernel

theorem tot15057 : totK PD2M8K2 D2M8K2.t15057 = [0, 0, 0, 253660564192, 475410210871, 111001875103, 2083783650, 0] := by
  decide +kernel

theorem rows15058 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15058 = true := by
  decide +kernel

theorem tot15058 : totK PD2M8K2 D2M8K2.t15058 = [0, 0, 117332931316, 397801642248, 297807951967, 49560335324, 2703270515, 0] := by
  decide +kernel

theorem rows15059 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15059 = true := by
  decide +kernel

theorem tot15059 : totK PD2M8K2 D2M8K2.t15059 = [0, 0, 187966245905, 457000738764, 229634303108, 16629160294, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
