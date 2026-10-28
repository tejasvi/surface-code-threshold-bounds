import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8340 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8340 = true := by
  decide +kernel

theorem tot8340 : totK PD2M8K2 D2M8K2.t8340 = [0, 207682843993, 467477867601, 211326386515, 12776041836, 0, 0, 0] := by
  decide +kernel

theorem rows8341 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8341 = true := by
  decide +kernel

theorem tot8341 : totK PD2M8K2 D2M8K2.t8341 = [0, 166605235652, 457836694125, 232087111122, 13494115512, 0, 0, 0] := by
  decide +kernel

theorem rows8342 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8342 = true := by
  decide +kernel

theorem tot8342 : totK PD2M8K2 D2M8K2.t8342 = [0, 182329972490, 463878857762, 236464307169, 13698234747, 0, 0, 0] := by
  decide +kernel

theorem rows8343 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8343 = true := by
  decide +kernel

theorem tot8343 : totK PD2M8K2 D2M8K2.t8343 = [0, 193002324280, 473599822565, 221264715242, 12443528988, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
