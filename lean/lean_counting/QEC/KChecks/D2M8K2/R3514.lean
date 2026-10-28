import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14056 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14056 = true := by
  decide +kernel

theorem tot14056 : totK PD2M8K2 D2M8K2.t14056 = [0, 0, 77960084248, 309341213682, 398197917063, 75809751586, 1271866555, 0] := by
  decide +kernel

theorem rows14057 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14057 = true := by
  decide +kernel

theorem tot14057 : totK PD2M8K2 D2M8K2.t14057 = [0, 0, 157149032236, 454677999666, 271065831205, 22067244629, 0, 0] := by
  decide +kernel

theorem rows14058 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14058 = true := by
  decide +kernel

theorem tot14058 : totK PD2M8K2 D2M8K2.t14058 = [0, 0, 178549153776, 458153729751, 253920695835, 13123399053, 0, 0] := by
  decide +kernel

theorem rows14059 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14059 = true := by
  decide +kernel

theorem tot14059 : totK PD2M8K2 D2M8K2.t14059 = [0, 180280610855, 442757799331, 260057918946, 35229041904, 4223973206, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
